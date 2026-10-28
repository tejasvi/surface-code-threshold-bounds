import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5516 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5516 = true := by
  decide +kernel

theorem tot5516 : totK PD2M8K2 D2M8K2.t5516 = [0, 193557772339, 457836933271, 196341535237, 12052611869, 0, 0, 0] := by
  decide +kernel

theorem rows5517 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5517 = true := by
  decide +kernel

theorem tot5517 : totK PD2M8K2 D2M8K2.t5517 = [153550581146, 440081010393, 272910328053, 34354163879, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5518 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5518 = true := by
  decide +kernel

theorem tot5518 : totK PD2M8K2 D2M8K2.t5518 = [169456228212, 435371906334, 253818782989, 20258282961, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5519 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5519 = true := by
  decide +kernel

theorem tot5519 : totK PD2M8K2 D2M8K2.t5519 = [91210733126, 363554533566, 361985497822, 69030748811, 1096505104, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
