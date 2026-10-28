import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13320 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13320 = true := by
  decide +kernel

theorem tot13320 : totK PD2M8K2 D2M8K2.t13320 = [0, 208838351816, 469908898836, 196347180028, 16572893578, 0, 0, 0] := by
  decide +kernel

theorem rows13321 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13321 = true := by
  decide +kernel

theorem tot13321 : totK PD2M8K2 D2M8K2.t13321 = [0, 189727797599, 462056898386, 220721947072, 12534051746, 0, 0, 0] := by
  decide +kernel

theorem rows13322 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13322 = true := by
  decide +kernel

theorem tot13322 : totK PD2M8K2 D2M8K2.t13322 = [0, 4188399740, 291948987241, 474398509867, 101712313184, 1369150432, 0, 0] := by
  decide +kernel

theorem rows13323 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13323 = true := by
  decide +kernel

theorem tot13323 : totK PD2M8K2 D2M8K2.t13323 = [0, 92968305029, 377734204850, 388756324420, 53221410043, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
