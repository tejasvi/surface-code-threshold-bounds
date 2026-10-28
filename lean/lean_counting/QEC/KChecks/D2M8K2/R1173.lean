import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4692 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4692 = true := by
  decide +kernel

theorem tot4692 : totK PD2M8K2 D2M8K2.t4692 = [0, 0, 324680298061, 528848566876, 77859829247, 0, 0, 0] := by
  decide +kernel

theorem rows4693 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4693 = true := by
  decide +kernel

theorem tot4693 : totK PD2M8K2 D2M8K2.t4693 = [0, 157245094994, 387601184825, 271938115411, 85750737456, 3880716147, 0, 0] := by
  decide +kernel

theorem rows4694 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4694 = true := by
  decide +kernel

theorem tot4694 : totK PD2M8K2 D2M8K2.t4694 = [0, 175170592170, 455478311951, 261774210986, 20395224636, 0, 0, 0] := by
  decide +kernel

theorem rows4695 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4695 = true := by
  decide +kernel

theorem tot4695 : totK PD2M8K2 D2M8K2.t4695 = [0, 81370462999, 351869226194, 382550028838, 86488973816, 1267860612, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
