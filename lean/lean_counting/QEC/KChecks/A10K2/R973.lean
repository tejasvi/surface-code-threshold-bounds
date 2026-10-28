import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3892 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3892 = true := by
  decide +kernel

theorem tot3892 : totK PA10K2 A10K2.t3892 = [0, 327737319032, 1532312975012, 2190121658128, 908098836422, 71491573315, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3893 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3893 = true := by
  decide +kernel

theorem tot3893 : totK PA10K2 A10K2.t3893 = [0, 0, 518200693992, 1965821286424, 2035711188061, 467817094647, 13816090359, 0, 0, 0] := by
  decide +kernel

theorem rows3894 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3894 = true := by
  decide +kernel

theorem tot3894 : totK PA10K2 A10K2.t3894 = [0, 0, 349482587980, 1581815363404, 2084651898429, 827195807774, 74707952681, 0, 0, 0] := by
  decide +kernel

theorem rows3895 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3895 = true := by
  decide +kernel

theorem tot3895 : totK PA10K2 A10K2.t3895 = [0, 0, 480149918198, 1839491658597, 2044826650974, 624380864894, 24453207590, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
