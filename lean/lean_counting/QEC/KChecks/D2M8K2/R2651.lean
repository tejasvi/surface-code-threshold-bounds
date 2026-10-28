import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10604 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10604 = true := by
  decide +kernel

theorem tot10604 : totK PD2M8K2 D2M8K2.t10604 = [0, 0, 259921263120, 489647474608, 153814709206, 8470662040, 0, 0] := by
  decide +kernel

theorem rows10605 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10605 = true := by
  decide +kernel

theorem tot10605 : totK PD2M8K2 D2M8K2.t10605 = [0, 121024145981, 354447044057, 317478513090, 87657769656, 3581949829, 0, 0] := by
  decide +kernel

theorem rows10606 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10606 = true := by
  decide +kernel

theorem tot10606 : totK PD2M8K2 D2M8K2.t10606 = [0, 177913886604, 433877090416, 266291961026, 30240056193, 0, 0, 0] := by
  decide +kernel

theorem rows10607 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10607 = true := by
  decide +kernel

theorem tot10607 : totK PD2M8K2 D2M8K2.t10607 = [0, 125165395975, 442810730562, 307637600618, 24756166325, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
