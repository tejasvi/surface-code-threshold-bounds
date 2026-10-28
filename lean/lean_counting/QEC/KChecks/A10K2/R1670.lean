import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6680 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6680 = true := by
  decide +kernel

theorem tot6680 : totK PA10K2 A10K2.t6680 = [0, 327234200007, 1522223098399, 2167132920191, 876940415310, 62762815243, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6681 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6681 = true := by
  decide +kernel

theorem tot6681 : totK PA10K2 A10K2.t6681 = [0, 0, 553002442111, 2017837623471, 1979372346934, 404556846181, 12224107035, 0, 0, 0] := by
  decide +kernel

theorem rows6682 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6682 = true := by
  decide +kernel

theorem tot6682 : totK PA10K2 A10K2.t6682 = [0, 319295482399, 1140877002331, 1599844367266, 1317580282779, 521622794479, 48886019071, 0, 0, 0] := by
  decide +kernel

theorem rows6683 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6683 = true := by
  decide +kernel

theorem tot6683 : totK PA10K2 A10K2.t6683 = [0, 527688658651, 1853604578522, 1850224418415, 479721594056, 18443208640, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
