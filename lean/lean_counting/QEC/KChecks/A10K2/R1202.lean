import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4808 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4808 = true := by
  decide +kernel

theorem tot4808 : totK PA10K2 A10K2.t4808 = [0, 114484931651, 830222650169, 2029700939728, 1654998286880, 370870148364, 12473006693, 0, 0, 0] := by
  decide +kernel

theorem rows4809 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4809 = true := by
  decide +kernel

theorem tot4809 : totK PA10K2 A10K2.t4809 = [0, 548894220459, 1899747454760, 1883373932119, 516510396395, 32035867417, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4810 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4810 = true := by
  decide +kernel

theorem tot4810 : totK PA10K2 A10K2.t4810 = [0, 119585100515, 1020783390654, 2148815666006, 1396013659681, 273505954585, 20300850681, 0, 0, 0] := by
  decide +kernel

theorem rows4811 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4811 = true := by
  decide +kernel

theorem tot4811 : totK PA10K2 A10K2.t4811 = [0, 254724154559, 1034178400806, 1826641912368, 1457369292132, 312386115854, 11151418702, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
