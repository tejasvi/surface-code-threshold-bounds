import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15844 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15844 = true := by
  decide +kernel

theorem tot15844 : totK PD2M8K2 D2M8K2.t15844 = [0, 0, 183134344404, 464569330545, 259031781925, 26378721989, 0, 0] := by
  decide +kernel

theorem rows15845 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15845 = true := by
  decide +kernel

theorem tot15845 : totK PD2M8K2 D2M8K2.t15845 = [0, 0, 88800000258, 417982493419, 350521448516, 33444410630, 0, 0] := by
  decide +kernel

theorem rows15846 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15846 = true := by
  decide +kernel

theorem tot15846 : totK PD2M8K2 D2M8K2.t15846 = [0, 0, 32087059031, 302024480296, 474328167738, 91723990697, 1415142070, 0] := by
  decide +kernel

theorem rows15847 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15847 = true := by
  decide +kernel

theorem tot15847 : totK PD2M8K2 D2M8K2.t15847 = [0, 0, 199169229581, 465689434700, 242070095870, 22918949651, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
