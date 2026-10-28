import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows288 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t288 = true := by
  decide +kernel

theorem tot288 : totK PA10K2 A10K2.t288 = [0, 0, 0, 472142187548, 1744848132269, 1833004910149, 444976529854, 30595569240, 0, 0] := by
  decide +kernel

theorem rows289 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t289 = true := by
  decide +kernel

theorem tot289 : totK PA10K2 A10K2.t289 = [0, 0, 0, 292959889058, 1516601191544, 2013032756726, 615934547776, 37652977581, 0, 0] := by
  decide +kernel

theorem rows290 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t290 = true := by
  decide +kernel

theorem tot290 : totK PA10K2 A10K2.t290 = [0, 0, 308867641608, 973974661214, 1171455100567, 1209770616746, 790372273889, 160040681813, 5676195732, 0] := by
  decide +kernel

theorem rows291 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t291 = true := by
  decide +kernel

theorem tot291 : totK PA10K2 A10K2.t291 = [0, 0, 499465683587, 1857138558650, 1987878947135, 520240827007, 17856659034, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
