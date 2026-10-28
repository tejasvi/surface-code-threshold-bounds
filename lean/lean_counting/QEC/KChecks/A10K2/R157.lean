import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows628 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t628 = true := by
  decide +kernel

theorem tot628 : totK PA10K2 A10K2.t628 = [0, 0, 0, 870034063248, 2306982127883, 1496748763263, 252890991993, 6904928264, 0, 0] := by
  decide +kernel

theorem rows629 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t629 = true := by
  decide +kernel

theorem tot629 : totK PA10K2 A10K2.t629 = [0, 0, 447867305066, 1735649882752, 2072281672314, 736999385820, 49931350110, 0, 0, 0] := by
  decide +kernel

theorem rows630 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t630 = true := by
  decide +kernel

theorem tot630 : totK PA10K2 A10K2.t630 = [0, 118410781347, 588892112331, 1632771878619, 2011841485075, 748177923971, 58173028014, 0, 0, 0] := by
  decide +kernel

theorem rows631 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t631 = true := by
  decide +kernel

theorem tot631 : totK PA10K2 A10K2.t631 = [0, 464459163498, 1850457779789, 1943547983667, 498697353323, 26491486257, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
