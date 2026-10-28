import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7492 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7492 = true := by
  decide +kernel

theorem tot7492 : totK PA10K2 A10K2.t7492 = [0, 0, 0, 459971114456, 1793628656853, 1937656782414, 506021312753, 32239129156, 0, 0] := by
  decide +kernel

theorem rows7493 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7493 = true := by
  decide +kernel

theorem tot7493 : totK PA10K2 A10K2.t7493 = [0, 0, 0, 572191705232, 1974918171255, 1893582509608, 400029688441, 13113133354, 0, 0] := by
  decide +kernel

theorem rows7494 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7494 = true := by
  decide +kernel

theorem tot7494 : totK PA10K2 A10K2.t7494 = [0, 0, 0, 520732119009, 1833533599841, 1832432489500, 444562783619, 30953568651, 0, 0] := by
  decide +kernel

theorem rows7495 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7495 = true := by
  decide +kernel

theorem tot7495 : totK PA10K2 A10K2.t7495 = [0, 0, 0, 111835199807, 1284818836653, 2264222732262, 844269790663, 64310687323, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
