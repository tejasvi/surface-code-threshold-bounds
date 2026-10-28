import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5708 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5708 = true := by
  decide +kernel

theorem tot5708 : totK PD2M8K2 D2M8K2.t5708 = [0, 49729852533, 342702964432, 455190749713, 58919365050, 0, 0, 0] := by
  decide +kernel

theorem rows5709 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5709 = true := by
  decide +kernel

theorem tot5709 : totK PD2M8K2 D2M8K2.t5709 = [0, 165214987511, 447536616752, 280948603388, 30282357663, 0, 0, 0] := by
  decide +kernel

theorem rows5710 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5710 = true := by
  decide +kernel

theorem tot5710 : totK PD2M8K2 D2M8K2.t5710 = [0, 123666052243, 444481760076, 314106481818, 32657517091, 0, 0, 0] := by
  decide +kernel

theorem rows5711 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5711 = true := by
  decide +kernel

theorem tot5711 : totK PD2M8K2 D2M8K2.t5711 = [0, 0, 221661554290, 503794054088, 165378111988, 5284349065, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
