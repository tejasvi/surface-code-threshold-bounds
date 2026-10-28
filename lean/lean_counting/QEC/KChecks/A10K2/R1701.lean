import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6804 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6804 = true := by
  decide +kernel

theorem tot6804 : totK PA10K2 A10K2.t6804 = [0, 867628670015, 2324238773227, 1643201684375, 295190324555, 6851704726, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6805 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6805 = true := by
  decide +kernel

theorem tot6805 : totK PA10K2 A10K2.t6805 = [0, 433723349535, 1793274057488, 2164629933664, 671405179934, 30118920131, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6806 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6806 = true := by
  decide +kernel

theorem tot6806 : totK PA10K2 A10K2.t6806 = [0, 512994577659, 1805243175236, 1808673252253, 520020397209, 52486959823, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6807 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6807 = true := by
  decide +kernel

theorem tot6807 : totK PA10K2 A10K2.t6807 = [0, 296957029898, 1466518587898, 2199690679457, 916440408281, 67798867528, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
