import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6412 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6412 = true := by
  decide +kernel

theorem tot6412 : totK PD2M8K2 D2M8K2.t6412 = [0, 0, 201262299226, 478883697956, 193214733375, 10901505393, 0, 0] := by
  decide +kernel

theorem rows6413 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6413 = true := by
  decide +kernel

theorem tot6413 : totK PD2M8K2 D2M8K2.t6413 = [0, 0, 194511627086, 466462091030, 210008848570, 12370590376, 0, 0] := by
  decide +kernel

theorem rows6414 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6414 = true := by
  decide +kernel

theorem tot6414 : totK PD2M8K2 D2M8K2.t6414 = [0, 0, 232263647622, 476198735329, 153518392070, 4940120826, 0, 0] := by
  decide +kernel

theorem rows6415 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6415 = true := by
  decide +kernel

theorem tot6415 : totK PD2M8K2 D2M8K2.t6415 = [0, 0, 213708623102, 482687644578, 165058343030, 5072912408, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
