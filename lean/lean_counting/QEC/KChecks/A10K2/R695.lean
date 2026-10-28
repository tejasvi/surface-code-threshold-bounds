import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2780 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2780 = true := by
  decide +kernel

theorem tot2780 : totK PA10K2 A10K2.t2780 = [327737319032, 1526561177781, 2178569594685, 869540839834, 70410343007, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2781 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2781 = true := by
  decide +kernel

theorem tot2781 : totK PA10K2 A10K2.t2781 = [0, 531483140817, 1960369945972, 2015636133840, 485471971372, 13816090359, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2782 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2782 = true := by
  decide +kernel

theorem tot2782 : totK PA10K2 A10K2.t2782 = [0, 525633807298, 1859673442315, 1943659819273, 605677272250, 49180423016, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2783 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2783 = true := by
  decide +kernel

theorem tot2783 : totK PA10K2 A10K2.t2783 = [0, 480149918198, 1778388973639, 1999442111616, 631845218478, 37876052273, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
