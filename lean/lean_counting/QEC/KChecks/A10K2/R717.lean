import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2868 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2868 = true := by
  decide +kernel

theorem tot2868 : totK PA10K2 A10K2.t2868 = [0, 0, 632920459214, 1803942938977, 1665178500287, 694720093346, 136147139169, 5685526223, 0, 0] := by
  decide +kernel

theorem rows2869 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2869 = true := by
  decide +kernel

theorem tot2869 : totK PA10K2 A10K2.t2869 = [0, 308899695994, 1199217957746, 1771624480441, 1323446191695, 415143375027, 31276155898, 0, 0, 0] := by
  decide +kernel

theorem rows2870 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2870 = true := by
  decide +kernel

theorem tot2870 : totK PA10K2 A10K2.t2870 = [0, 487128049630, 1875615334408, 2036876581050, 556411211597, 19117496088, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2871 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2871 = true := by
  decide +kernel

theorem tot2871 : totK PA10K2 A10K2.t2871 = [0, 0, 573507177065, 2018569641837, 1798661826499, 410850443738, 25734533292, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
