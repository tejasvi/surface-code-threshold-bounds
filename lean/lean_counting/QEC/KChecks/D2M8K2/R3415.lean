import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13660 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13660 = true := by
  decide +kernel

theorem tot13660 : totK PD2M8K2 D2M8K2.t13660 = [0, 178164890206, 449546155434, 235662092754, 17517334812, 0, 0, 0] := by
  decide +kernel

theorem rows13661 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13661 = true := by
  decide +kernel

theorem tot13661 : totK PD2M8K2 D2M8K2.t13661 = [0, 63491650360, 346128965984, 409506092249, 69640247373, 1075657031, 0, 0] := by
  decide +kernel

theorem rows13662 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13662 = true := by
  decide +kernel

theorem tot13662 : totK PD2M8K2 D2M8K2.t13662 = [0, 25789203758, 279724377311, 453554536951, 110584656076, 3804183361, 0, 0] := by
  decide +kernel

theorem rows13663 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13663 = true := by
  decide +kernel

theorem tot13663 : totK PD2M8K2 D2M8K2.t13663 = [0, 192857260137, 461436780601, 239093929569, 20698318675, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
