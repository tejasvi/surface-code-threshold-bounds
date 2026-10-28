import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10060 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10060 = true := by
  decide +kernel

theorem tot10060 : totK PD2M8K2 D2M8K2.t10060 = [0, 153440597783, 329672509808, 204064211152, 138619283506, 90561717777, 6818291842, 0] := by
  decide +kernel

theorem rows10061 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10061 = true := by
  decide +kernel

theorem tot10061 : totK PD2M8K2 D2M8K2.t10061 = [0, 184475809727, 477257272397, 228035254238, 13961838122, 0, 0, 0] := by
  decide +kernel

theorem rows10062 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10062 = true := by
  decide +kernel

theorem tot10062 : totK PD2M8K2 D2M8K2.t10062 = [0, 87744675159, 392151649746, 371000493226, 64276896660, 3626128243, 0, 0] := by
  decide +kernel

theorem rows10063 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10063 = true := by
  decide +kernel

theorem tot10063 : totK PD2M8K2 D2M8K2.t10063 = [0, 0, 161755933770, 446672665533, 272002440646, 22923882582, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
