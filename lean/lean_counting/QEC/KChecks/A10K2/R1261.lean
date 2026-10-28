import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5044 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5044 = true := by
  decide +kernel

theorem tot5044 : totK PA10K2 A10K2.t5044 = [0, 0, 452011919396, 1797874442990, 1986835772976, 519954755291, 31222411477, 0, 0, 0] := by
  decide +kernel

theorem rows5045 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5045 = true := by
  decide +kernel

theorem tot5045 : totK PA10K2 A10K2.t5045 = [0, 0, 123691382636, 952729313322, 1939260842173, 1318217205306, 335787363425, 25239774317, 0, 0] := by
  decide +kernel

theorem rows5046 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5046 = true := by
  decide +kernel

theorem tot5046 : totK PA10K2 A10K2.t5046 = [0, 0, 212357658455, 1062280427036, 1897524541963, 1245446554878, 213519507819, 5410721913, 0, 0] := by
  decide +kernel

theorem rows5047 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5047 = true := by
  decide +kernel

theorem tot5047 : totK PA10K2 A10K2.t5047 = [0, 0, 530766373319, 1780875879875, 1845177008935, 518516613473, 31608797364, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
