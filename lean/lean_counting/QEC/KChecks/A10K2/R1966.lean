import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7864 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7864 = true := by
  decide +kernel

theorem tot7864 : totK PA10K2 A10K2.t7864 = [0, 0, 487588809585, 1786047385249, 1977031274998, 655809746756, 30502495739, 0, 0, 0] := by
  decide +kernel

theorem rows7865 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7865 = true := by
  decide +kernel

theorem tot7865 : totK PA10K2 A10K2.t7865 = [0, 0, 0, 788715548212, 2204458501769, 1629578886358, 276694035958, 7047025452, 0, 0] := by
  decide +kernel

theorem rows7866 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7866 = true := by
  decide +kernel

theorem tot7866 : totK PA10K2 A10K2.t7866 = [0, 0, 540648836417, 1850695849224, 1888093255854, 639378842516, 56516890963, 0, 0, 0] := by
  decide +kernel

theorem rows7867 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7867 = true := by
  decide +kernel

theorem tot7867 : totK PA10K2 A10K2.t7867 = [0, 0, 327291078893, 1516099827333, 2160383535762, 871438211607, 62723358326, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
