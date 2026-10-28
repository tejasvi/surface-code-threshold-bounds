import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5572 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5572 = true := by
  decide +kernel

theorem tot5572 : totK PD2M8K2 D2M8K2.t5572 = [0, 181452171178, 458153914057, 256357654358, 25301490791, 0, 0, 0] := by
  decide +kernel

theorem rows5573 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5573 = true := by
  decide +kernel

theorem tot5573 : totK PD2M8K2 D2M8K2.t5573 = [54494369517, 215177080496, 387072593975, 227181024230, 17476474534, 0, 0, 0] := by
  decide +kernel

theorem rows5574 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5574 = true := by
  decide +kernel

theorem tot5574 : totK PD2M8K2 D2M8K2.t5574 = [192170748150, 483468890695, 208635617008, 11034354488, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5575 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5575 = true := by
  decide +kernel

theorem tot5575 : totK PD2M8K2 D2M8K2.t5575 = [170686001626, 465699336811, 243341170310, 12609838461, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
