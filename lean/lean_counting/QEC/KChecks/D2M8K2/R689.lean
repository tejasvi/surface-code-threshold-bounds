import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2756 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2756 = true := by
  decide +kernel

theorem tot2756 : totK PD2M8K2 D2M8K2.t2756 = [0, 0, 196640971118, 462857533403, 223909289082, 15844255384, 0, 0] := by
  decide +kernel

theorem rows2757 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2757 = true := by
  decide +kernel

theorem tot2757 : totK PD2M8K2 D2M8K2.t2757 = [0, 0, 178366171919, 460296115779, 225393838267, 16702988424, 0, 0] := by
  decide +kernel

theorem rows2758 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2758 = true := by
  decide +kernel

theorem tot2758 : totK PD2M8K2 D2M8K2.t2758 = [0, 0, 34116403298, 389428774000, 404220002986, 44336759198, 0, 0] := by
  decide +kernel

theorem rows2759 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2759 = true := by
  decide +kernel

theorem tot2759 : totK PD2M8K2 D2M8K2.t2759 = [0, 71794763572, 151299444852, 233623069264, 333681428183, 91509919215, 1429815836, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
