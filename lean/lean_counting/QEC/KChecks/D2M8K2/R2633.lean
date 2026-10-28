import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10532 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10532 = true := by
  decide +kernel

theorem tot10532 : totK PD2M8K2 D2M8K2.t10532 = [0, 84943629437, 379151905485, 371033824462, 82597782807, 10444649207, 0, 0] := by
  decide +kernel

theorem rows10533 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10533 = true := by
  decide +kernel

theorem tot10533 : totK PD2M8K2 D2M8K2.t10533 = [0, 0, 174106648810, 458230202471, 250945568101, 14929139160, 0, 0] := by
  decide +kernel

theorem rows10534 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10534 = true := by
  decide +kernel

theorem tot10534 : totK PD2M8K2 D2M8K2.t10534 = [0, 7543284815, 176314025146, 469221748413, 233448498669, 10460337654, 0, 0] := by
  decide +kernel

theorem rows10535 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10535 = true := by
  decide +kernel

theorem tot10535 : totK PD2M8K2 D2M8K2.t10535 = [0, 203467923815, 459347805503, 233651172172, 23389423654, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
