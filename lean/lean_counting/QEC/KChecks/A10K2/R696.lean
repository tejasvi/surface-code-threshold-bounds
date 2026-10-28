import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2784 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2784 = true := by
  decide +kernel

theorem tot2784 : totK PA10K2 A10K2.t2784 = [0, 0, 759112935421, 2226557691232, 1581795944154, 273120838901, 6904928264, 0, 0, 0] := by
  decide +kernel

theorem rows2785 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2785 = true := by
  decide +kernel

theorem tot2785 : totK PA10K2 A10K2.t2785 = [0, 474622751017, 1688442523882, 1991018331155, 828476430038, 82106869626, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2786 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2786 = true := by
  decide +kernel

theorem tot2786 : totK PA10K2 A10K2.t2786 = [0, 118912563486, 976104608056, 2177331480763, 1505746413393, 253546596845, 7047025452, 0, 0, 0] := by
  decide +kernel

theorem rows2787 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2787 = true := by
  decide +kernel

theorem tot2787 : totK PA10K2 A10K2.t2787 = [0, 389538896892, 1587235717528, 2034116560999, 880779223613, 85649981130, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
