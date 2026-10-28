import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1664 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1664 = true := by
  decide +kernel

theorem tot1664 : totK PD2M8K2 D2M8K2.t1664 = [0, 0, 173916283009, 475272519789, 240108349383, 16617089898, 0, 0] := by
  decide +kernel

theorem rows1665 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1665 = true := by
  decide +kernel

theorem tot1665 : totK PD2M8K2 D2M8K2.t1665 = [0, 0, 170375439666, 473552579019, 237623722505, 13028250117, 0, 0] := by
  decide +kernel

theorem rows1666 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1666 = true := by
  decide +kernel

theorem tot1666 : totK PD2M8K2 D2M8K2.t1666 = [0, 0, 155794207477, 445562070319, 267181672031, 21396622169, 0, 0] := by
  decide +kernel

theorem rows1667 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1667 = true := by
  decide +kernel

theorem tot1667 : totK PD2M8K2 D2M8K2.t1667 = [0, 0, 0, 245861108286, 456823427759, 126862075604, 4879840392, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
