#include <ESP32Servo.h>
#define SOUND_SPEED 0.034
// ================= SERVOS =================
Servo Lucas;
Servo Continu2;
Servo Burak;
Servo Slope;

// ================= DISTANCE SENSOR =================
const int trigPin = 20;
const int echoPin = 19;
float seuilMin = 9.10;
float seuilMax = 9.30;
long duration;
float distanceCm;
int validCount = 0;
const int requiredHits = 2;
const float targetDist    = 9.15;
const float rampStartDist = 15.0;

// ================= SERVO PINS =================
const int LucasPin = 18;
const int BurakPin = 14;
const int Continu2Pin = 5;
const int SlopePin = 17;

// ================= EMERGENCY BUTTON PIN =================
const int EMERGENCY_PIN = 16;

// ================= BURAK ANGLES =================
int Angle1 = 4;
int Angle2 = 35;
int Angle3 = 102;
int Angle4 = 132;
int AngleRepos = 69;

// Queue for Burak commands
char cmdQ[4] = {'0','0','0', '0'};
char pendingCmd = 0;

// ================= SLOPE ANGLES =================
int SlopeAngle1 = 45;
int SlopeAngle2 = 85;

// ================= SPEED CONSTANTS =================
const int LUCAS_SPEED = 110;
const int LUCAS_STOP = 90;
const int CONT2_MAX = 180;
const int CONT2_RUN = 170;
const int CONT2_STOP = 90;
int cont2Speed = CONT2_RUN;
int lucaspeed = LUCAS_SPEED;
const float KP = 10.0; 
const int SPEED_MIN_RUN = 106; 
#define SPEED_RUN     170   


// ================= STATES =================
enum State {
  WAIT_CONFIG,
  WAIT_REPOS_DELAY,
  DEPART,
  RAMP_DOWN,
  PI_EXCHANGE,
  MOVE_BURAK,
  TEST_MODE,
  EMERGENCY
};

State state = WAIT_CONFIG;

// ================= DELAYS =================
unsigned long reposStartMs       = 0;
const unsigned long reposDelay   = 2000;

// ================= BINS STRUCT =================
struct ComboBin { int diam; int length; bool valid; };

ComboBin bins[4];
int receivedCount = 0;
bool binsFilled   = false;

// ================= EMERGENCY LOGIC =================
int lastButtonState = HIGH;

// ================= SEND SPEED OF CONTINU2 =================
void sendSPD() {
  const float maxRpm = 25.0;
  float rpm = 0.0;

  if (cont2Speed > CONT2_STOP) {
    rpm = maxRpm * (cont2Speed - CONT2_STOP) / 90.0;
  } else if (cont2Speed < CONT2_STOP) {
    rpm = -maxRpm * (CONT2_STOP - cont2Speed) / 90.0;
  } else {
    rpm = 0.0;
  }

  int rpmInt = (int)rpm;
  float speed2 = 0.007*rpm*0.5;
  Serial.print("SPD:");
  Serial.println(rpmInt);
  Serial.print("SPD_MS:");
  Serial.println(speed2);
}

// ================= SEND SPEED OF LUCA =================
void LucaSendSPD() {
  const float maxRpm2 = 30.0;
  float rpm2 = 0.0;

  if (lucaspeed > CONT2_STOP) {
    rpm2 = maxRpm2 * (lucaspeed - CONT2_STOP) / 90.0;
  } else if (lucaspeed < CONT2_STOP) {
    rpm2 = -maxRpm2 * (CONT2_STOP - lucaspeed) / 90.0;
  } else {
    rpm2 = 0.0;
  }

  int rpmInt2 = (int)rpm2;
  
  Serial.print("LUCAS_SPD:");
  Serial.println(rpmInt2);
}

// ================= BIN REPORT =================
void reportBIN(int id) {
  Serial.print("BIN:");
  Serial.println(id);
}

// ================= DISTANCE MEASUREMENT =================
void measureDistance() {
  digitalWrite(trigPin, LOW);
  delayMicroseconds(2);
  digitalWrite(trigPin, HIGH);
  delayMicroseconds(10);
  digitalWrite(trigPin, LOW);

  duration = pulseIn(echoPin, HIGH, 30000);
  if (duration == 0) {
    distanceCm = 999;
  } else {
    distanceCm = duration * SOUND_SPEED / 2.0;
  }

  Serial.print("DIST:");
  Serial.println(distanceCm);
}

// ================= SEND STATE OF THE MOTORS =================
unsigned long lastStateSend = 0;


// ================= QUEUE MANAGEMENT =================
void shiftAfterMove() {
  cmdQ[3] = cmdQ[2];
  cmdQ[2] = cmdQ[1];
  cmdQ[1] = cmdQ[0];
  cmdQ[0] = pendingCmd;
  pendingCmd = 0;
}

// ================= ENTER RAMP DOWN STATE =================
void enterRampDown() {
  validCount = 0;
  state = DEPART;
}

// ================= CONFIGURATION READING =================
bool parseComboLine(const String &line, int &diamOut, int &lenOut) {
  int dPos = line.indexOf("D=M");
  int lPos = line.indexOf(";L=");
  int mPos = line.indexOf(";M=");

  if (dPos == -1 || lPos == -1 || mPos == -1) return false;

  diamOut = line.substring(dPos + 3, lPos).toInt();
  lenOut  = line.substring(lPos + 3, mPos).toInt();

  return (diamOut > 0 && lenOut > 0);
}

// ================= STORE COMBINATIONS INTO BINS =================
void storeIntoNextBin(int diam, int len) {
  if (receivedCount < 4) {
    bins[receivedCount] = {diam, len, true};
    receivedCount++;

    if (receivedCount == 4) {
      binsFilled   = true;
      reposStartMs = millis();
      state        = DEPART;
    }
  }
}

// ================= CLASSIFY SCREW INTO BIN =================
int classifyScrew(int diam, int len) {
  if (!binsFilled) return 5;

  for (int i = 0; i < 4; i++) {
    if (bins[i].valid && bins[i].diam == diam && bins[i].length == len)
      return i + 1;
  }
  return 5;
}

// ================= READ MESSAGE FROM RASPBERRY PI =================
bool parsePiLineClassic(const String &v, int &lengthOut, int &diamOut) {
  int sep = v.indexOf(';');
  if (sep == -1) return false;

  lengthOut = v.substring(0, sep).toInt();
  diamOut   = v.substring(sep + 1).toInt();
  return true;
}

bool parsePiLineClassic2(const String &v, int &lengthOut, int &diamOut, int &flagOut) {
  int sep1 = v.indexOf(';');
  if (sep1 == -1) return false;

  int sep2 = v.indexOf(';', sep1 + 1);
  if (sep2 == -1) return false;

  lengthOut = v.substring(0, sep1).toInt();
  diamOut   = v.substring(sep1 + 1, sep2).toInt();
  flagOut   = v.substring(sep2 + 1).toInt();

  return true;
}

// ========================================================================================================
//                                              SETUP
// ========================================================================================================
void setup() {
  Serial.begin(115200);
  Serial2.begin(115200, SERIAL_8N1, 8, 9);   //8  4e,  9 5e

  Lucas.attach(LucasPin);
  Burak.attach(BurakPin);
  Continu2.attach(Continu2Pin);
  Slope.attach(SlopePin);

  pinMode(EMERGENCY_PIN, INPUT_PULLUP);

  pinMode(trigPin, OUTPUT);
  pinMode(echoPin, INPUT);

  Lucas.write(LUCAS_STOP);
  Burak.write(AngleRepos);
  Continu2.write(CONT2_STOP);
  cont2Speed = CONT2_STOP;
  lucaspeed = LUCAS_STOP;
  Slope.write(SlopeAngle1);
  sendSPD();
  LucaSendSPD();
  for (int i = 0; i < 4; i++)
    bins[i] = {0, 0, false};

  lastButtonState = digitalRead(EMERGENCY_PIN);

  Serial.println("SETUP DONE");
}

// ========================================================================================================
//                                              LOOP
// ========================================================================================================
void loop() {

  // ===== Periodic motor state telemetry =====
  if (millis() - lastStateSend > 200) {
    lastStateSend = millis();
    sendSPD();
    LucaSendSPD();
  }

  // ===== EMERGENCY BUTTON HANDLING =====
  int btn = digitalRead(EMERGENCY_PIN);

  // Detect a "click" 
  if (btn == HIGH && lastButtonState == LOW) {
    if (state != EMERGENCY) {
      // First click: activate EMERGENCY mode
      state = EMERGENCY;
      Serial.println(">> EMERGENCY MODE ACTIVATED <<");
    } else {
      // Second click: restart the ESP32
      Serial.println(">> EMERGENCY CLEARED, RESTARTING ESP32 <<");
      ESP.restart();
    }
  }

  lastButtonState = btn;

  // ===== SWITCH WITH ALL OUR STATES =====
  switch (state) {

    // ----------- CONFIGURATION OF THE CHOSEN SCREWS, COMES FROM THE PYTHON INTERFACE ----------- //
    case WAIT_CONFIG:
      if (Serial.available()) {
        String line = Serial.readStringUntil('\n');
        line.trim();

        if (line == "TEST") {
          Serial.println("<< TEST MODE >>");
          state = TEST_MODE;
          break;
        } else {
          int d, l;
          if (parseComboLine(line, d, l)) {
            Lucas.write(LUCAS_SPEED);
            Serial.println("MOTOR:servo_13kg_1:1");
            storeIntoNextBin(d, l);
          }

        }
      }
      break;

    // ----------- DELAY BEFORE START ----------- //
    case WAIT_REPOS_DELAY:
      if (millis() - reposStartMs >= reposDelay)
        enterRampDown();
      break;

    // ----------- MANUAL CONTROL TO CHECK IF EVERY SERVO WORK ----------- //
    case TEST_MODE:
      if (Serial.available()) {
        String cmd = Serial.readStringUntil('\n');
        cmd.trim();

        if (cmd == "STOP") {
          Lucas.write(90);
          Continu2.write(CONT2_STOP);
          Burak.write(AngleRepos);
          Slope.write(SlopeAngle1);
          cont2Speed = CONT2_STOP;
          lucaspeed = 90;
          Serial.println("MOTOR:servo_35kg:0"); 
          Serial.println("MOTOR:servo_13kg_1:0");  
          LucaSendSPD();        
          sendSPD();
          Serial.println("[TEST] STOPPED");
        }
        else if (cmd == "EXIT") {
          Serial.println("[TEST] EXIT");
          state = WAIT_CONFIG;
        }
        else if (cmd.startsWith("L=")) {
          lucaspeed = cmd.substring(2).toInt();
          Lucas.write(lucaspeed);
          Serial.println("MOTOR:servo_13kg_1:1");
          LucaSendSPD(); 
        }
        else if (cmd.startsWith("C=")) {
          cont2Speed = cmd.substring(2).toInt();
          Continu2.write(cont2Speed);
          Serial.println("MOTOR:servo_35kg:1");
          sendSPD();
        }
        else if (cmd.startsWith("B=")) {
          Burak.write(cmd.substring(2).toInt());
          Serial.println("MOTOR:servo_3A1:1");
          delay(100);
          Serial.println("MOTOR:servo_3A1:0");

        }
        else if (cmd.startsWith("D=")) {
          int angleD = cmd.substring(2).toInt();
          Slope.write(angleD);
          Serial.println("MOTOR:servo_3A2:1");
          delay(100);
          Serial.println("MOTOR:servo_3A2:0");
        }
      }
      break;

    // ----------- START CONVEYOR ----------- //
    case DEPART:
      Lucas.write(LUCAS_SPEED);
      Continu2.write(CONT2_RUN);
      cont2Speed = CONT2_RUN;
      sendSPD();
      Serial.println("MOTOR:servo_35kg:1");

      delay(700);
      state = RAMP_DOWN;
      break;

    // ----------- STOP CONVEYOR BASED ON DISTANCE ----------- //
    case RAMP_DOWN: {
      Lucas.write(LUCAS_SPEED);

      measureDistance();
      if (distanceCm != 999 && distanceCm > targetDist) {

      // Erreur = combien je suis trop loin de la cible
        float error = distanceCm - targetDist;

        // On sature l'erreur pour ne pas dépasser la zone de ramp
        float maxError = rampStartDist - targetDist;
        if (error > maxError) error = maxError;
        if (error < 0)        error = 0;  // sécurité

        // Commande P : speed = min_run + KP * error
        float cmd = SPEED_MIN_RUN + KP * error;

        // Saturation de la vitesse entre min_run et run
        if (cmd > SPEED_RUN)     cmd = SPEED_RUN;
        if (cmd < SPEED_MIN_RUN) cmd = SPEED_MIN_RUN;

        int newSpeed = (int)cmd;

        //Serial.print("dist = ");
        //Serial.print(distanceCm);
        //Serial.print("  err = ");
        //Serial.print(error);
        //Serial.print("  speed = ");
        //Serial.println(newSpeed);

        Continu2.write(newSpeed);
      }
      if (distanceCm >= seuilMin && distanceCm <= seuilMax) {
        validCount++;
        Serial.print("VALID HIT ");
        Serial.println(validCount);
      } else {
        validCount = 0;
      }

      if (validCount >= requiredHits) {
        Continu2.write(CONT2_STOP);
        cont2Speed = CONT2_STOP;
        Serial.println("MOTOR:servo_35kg:0");
        sendSPD();
        Serial.println("== DOUBLE DISTANCE VALIDATION -> STOP & PI_EXCHANGE ==");
        validCount = 0;
        state = PI_EXCHANGE;
      }

      delay(10);
      break;
    }

    /*
    // ----------- EXCHANGE WITH RASPBERRY PI ----------- //
    case PI_EXCHANGE: {

      // Request measurement from Raspberry Pi
      Slope.write(85);

      Serial2.println("1");
      Serial.println("MOTOR:servo_3A2:1");
      delay(100);
      Serial.println("MOTOR:servo_3A2:0");
      delay(1500);
      Serial.println("MOTOR:servo_3A2:1");
      Slope.write(45);
      Serial.println("MOTOR:servo_3A2:0");

      // Read the PI message
      String v = Serial2.readStringUntil('\n');
      v.trim();

      if (v.length() > 0) {
        int lenPi, diamPi;
        if (parsePiLineClassic(v, lenPi, diamPi)) {

          if (diamPi == 0 && lenPi == 0) {
            reportBIN(5);
            pendingCmd = '0';
            state = MOVE_BURAK;
            break;
          }

          int binId = classifyScrew(diamPi, lenPi);
          pendingCmd = (binId >= 1 && binId <= 4) ? char('0' + binId) : '0';

          reportBIN(binId);
          state = MOVE_BURAK;
        }
      }
      break;
    }
*/
    case PI_EXCHANGE: {
      Serial2.println("1");
      Lucas.write(88);
      delay(100);
      Slope.write(85);
      delay(500);
      Slope.write(45);
      delay(500);
      Slope.write(85);
      delay(500);
      Slope.write(45);
      delay(1400);
      
      Serial.println("MOTOR:servo_3A2:1");
      delay(100);
      Serial.println("MOTOR:servo_3A2:0");
      delay(1000);
      // Read the PI message
      String v = Serial2.readStringUntil('\n');
      v.trim();

      if (v.length() > 0) {
        int lenPi, diamPi, flagPi;
        if (parsePiLineClassic2(v, lenPi, diamPi, flagPi)) {

          if (flagPi == 1) {

            Continu2.write(CONT2_RUN);
            cont2Speed = CONT2_RUN;
            sendSPD();
            Serial.println("MOTOR:servo_35kg:1");

            delay(3000);  // faut qu'on adapte ca 
            state = DEPART;
            break;
          }

          if (diamPi == 0 && lenPi == 0) {
            //reportBIN(5);
            pendingCmd = '0';
            state = MOVE_BURAK;
            break;
          }

          int binId = classifyScrew(diamPi, lenPi);
          pendingCmd = (binId >= 1 && binId <= 4) ? char('0' + binId) : '0';

          reportBIN(binId);
          state = MOVE_BURAK;
        }
      }
      break;
    }

    // ----------- MOVE BURAK SERVO AND SHIFT QUEUE ----------- //
    case MOVE_BURAK:
      shiftAfterMove();
      switch (cmdQ[3]) {
        case '1': Burak.write(Angle1);   break;
        case '2': Burak.write(Angle2);   break;
        case '3': Burak.write(Angle3);   break;
        case '4': Burak.write(Angle4);   break;
        default : Burak.write(AngleRepos); break;
      }
      Serial.println("MOTOR:servo_3A1:1");
      delay(100);
      Serial.println("MOTOR:servo_3A1:0");

      
      delay(300);
      state = DEPART;
      break;

    // ----------- EMERGENCY STATE ----------- //
    case EMERGENCY: {
      Lucas.write(90);
      Continu2.write(90);
      cont2Speed = 90;
      lucaspeed = 90;
      Burak.write(Angle1);
      Slope.write(SlopeAngle1);
      Serial.println("MOTOR:servo_35kg:0");
      Serial.println("MOTOR:servo_3A1:0");
      Serial.println("MOTOR:servo_3A2:0");
      Serial.println("MOTOR:servo_13kg_1:0");  

      sendSPD();
      LucaSendSPD();

      static bool msgOnce = false;
      if (!msgOnce) {
        Serial.println("!! EMERGENCY STOP !!");
        Serial.println("Press and release the emergency button again to restart.");
        msgOnce = true;
      }
      break;
    }
  }
}
