import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7640 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7640 = true := by
  decide +kernel

theorem tot7640 : totK PA10K2 A10K2.t7640 = [0, 0, 610900211470, 2013391381292, 1898434989395, 488284994938, 33495596084, 0, 0, 0] := by
  decide +kernel

theorem rows7641 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7641 = true := by
  decide +kernel

theorem tot7641 : totK PA10K2 A10K2.t7641 = [0, 0, 0, 816477413753, 2353343110051, 1714957381561, 255997440779, 0, 0, 0] := by
  decide +kernel

theorem rows7642 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7642 = true := by
  decide +kernel

theorem tot7642 : totK PA10K2 A10K2.t7642 = [0, 0, 0, 427183871245, 1709167292498, 2055486114648, 715025563955, 47540011751, 0, 0] := by
  decide +kernel

theorem rows7643 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7643 = true := by
  decide +kernel

theorem tot7643 : totK PA10K2 A10K2.t7643 = [0, 0, 0, 460054054256, 1780738193963, 1947941474727, 507691591331, 26479096260, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
