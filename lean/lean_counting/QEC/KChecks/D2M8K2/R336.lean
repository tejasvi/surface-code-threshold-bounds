import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1344 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1344 = true := by
  decide +kernel

theorem tot1344 : totK PD2M8K2 D2M8K2.t1344 = [0, 84265373804, 325183523824, 363898973744, 93778790655, 3804183361, 0, 0] := by
  decide +kernel

theorem rows1345 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1345 = true := by
  decide +kernel

theorem tot1345 : totK PD2M8K2 D2M8K2.t1345 = [0, 178057034241, 458949145089, 250161984843, 20578879967, 0, 0, 0] := by
  decide +kernel

theorem rows1346 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1346 = true := by
  decide +kernel

theorem tot1346 : totK PD2M8K2 D2M8K2.t1346 = [0, 155099038844, 443687048386, 268471609161, 24562280049, 0, 0, 0] := by
  decide +kernel

theorem rows1347 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1347 = true := by
  decide +kernel

theorem tot1347 : totK PD2M8K2 D2M8K2.t1347 = [0, 0, 248712409553, 479407462553, 131001841886, 4931404646, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
