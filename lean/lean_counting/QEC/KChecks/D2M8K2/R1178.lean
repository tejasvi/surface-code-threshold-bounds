import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4712 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4712 = true := by
  decide +kernel

theorem tot4712 : totK PD2M8K2 D2M8K2.t4712 = [0, 0, 0, 315123895929, 525485534218, 76825949638, 0, 0] := by
  decide +kernel

theorem rows4713 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4713 = true := by
  decide +kernel

theorem tot4713 : totK PD2M8K2 D2M8K2.t4713 = [0, 0, 159781670224, 405423489908, 280956862850, 65076962045, 1415142070, 0] := by
  decide +kernel

theorem rows4714 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4714 = true := by
  decide +kernel

theorem tot4714 : totK PD2M8K2 D2M8K2.t4714 = [0, 0, 196714938986, 479345724962, 228332337271, 11950516718, 0, 0] := by
  decide +kernel

theorem rows4715 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4715 = true := by
  decide +kernel

theorem tot4715 : totK PD2M8K2 D2M8K2.t4715 = [0, 0, 56171479306, 396993965447, 404432793617, 54883706015, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
