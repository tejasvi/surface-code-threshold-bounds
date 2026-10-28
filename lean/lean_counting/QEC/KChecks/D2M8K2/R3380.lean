import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13520 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13520 = true := by
  decide +kernel

theorem tot13520 : totK PD2M8K2 D2M8K2.t13520 = [190035171307, 461678613462, 237548535143, 17033427234, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13521 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13521 = true := by
  decide +kernel

theorem tot13521 : totK PD2M8K2 D2M8K2.t13521 = [8130385210, 299810747821, 486241291449, 108733763840, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows13522 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13522 = true := by
  decide +kernel

theorem tot13522 : totK PD2M8K2 D2M8K2.t13522 = [0, 198405711103, 476997106632, 191027144849, 7442000727, 0, 0, 0] := by
  decide +kernel

theorem rows13523 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13523 = true := by
  decide +kernel

theorem tot13523 : totK PD2M8K2 D2M8K2.t13523 = [0, 198970253722, 472838250194, 215171802526, 14707859566, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
