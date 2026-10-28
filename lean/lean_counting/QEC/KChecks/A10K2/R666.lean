import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2664 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2664 = true := by
  decide +kernel

theorem tot2664 : totK PA10K2 A10K2.t2664 = [0, 0, 454041036917, 1784765069964, 1986946291401, 553840374624, 32523532663, 0, 0, 0] := by
  decide +kernel

theorem rows2665 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2665 = true := by
  decide +kernel

theorem tot2665 : totK PA10K2 A10K2.t2665 = [0, 0, 84169918459, 855801384200, 2044956024879, 1471076983339, 350404068616, 25565504801, 0, 0] := by
  decide +kernel

theorem rows2666 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2666 = true := by
  decide +kernel

theorem tot2666 : totK PA10K2 A10K2.t2666 = [0, 0, 163761173604, 1053891448198, 1950663285973, 1212620635013, 215987531889, 5517381808, 0, 0] := by
  decide +kernel

theorem rows2667 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2667 = true := by
  decide +kernel

theorem tot2667 : totK PA10K2 A10K2.t2667 = [0, 0, 578600964295, 1874183435837, 1777266795892, 507739940574, 31936107789, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
