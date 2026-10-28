import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2536 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2536 = true := by
  decide +kernel

theorem tot2536 : totK PA10K2 A10K2.t2536 = [0, 0, 81384195587, 699971229217, 1822007099488, 1540613953395, 386369964601, 15847424528, 0, 0] := by
  decide +kernel

theorem rows2537 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2537 = true := by
  decide +kernel

theorem tot2537 : totK PA10K2 A10K2.t2537 = [0, 0, 548074569033, 1843607544185, 1768311129466, 470537457390, 31821298896, 0, 0, 0] := by
  decide +kernel

theorem rows2538 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2538 = true := by
  decide +kernel

theorem tot2538 : totK PA10K2 A10K2.t2538 = [0, 0, 107732319244, 1245143840819, 2291832472696, 873465322246, 65663687045, 0, 0, 0] := by
  decide +kernel

theorem rows2539 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2539 = true := by
  decide +kernel

theorem tot2539 : totK PA10K2 A10K2.t2539 = [0, 0, 410527057046, 1466250555535, 1886971174069, 944509665157, 154547954951, 5685526223, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
