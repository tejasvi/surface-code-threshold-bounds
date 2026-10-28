import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows604 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t604 = true := by
  decide +kernel

theorem tot604 : totK PA10K2 A10K2.t604 = [0, 0, 513898091978, 1818208654870, 1858476803170, 513177286336, 31608797364, 0, 0, 0] := by
  decide +kernel

theorem rows605 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t605 = true := by
  decide +kernel

theorem tot605 : totK PA10K2 A10K2.t605 = [0, 0, 183386266931, 1338718371000, 2195262716703, 846420515801, 59823752816, 0, 0, 0] := by
  decide +kernel

theorem rows606 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t606 = true := by
  decide +kernel

theorem tot606 : totK PA10K2 A10K2.t606 = [0, 0, 397509360782, 1392984973111, 1860243291920, 958403510514, 159262222042, 5546304973, 0, 0] := by
  decide +kernel

theorem rows607 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t607 = true := by
  decide +kernel

theorem tot607 : totK PA10K2 A10K2.t607 = [0, 304661711030, 1037819207222, 1673984121314, 1618287305411, 491122661032, 29791859037, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
