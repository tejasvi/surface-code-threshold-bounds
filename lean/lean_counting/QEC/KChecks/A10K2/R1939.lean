import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7756 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7756 = true := by
  decide +kernel

theorem tot7756 : totK PA10K2 A10K2.t7756 = [0, 0, 0, 473180971226, 1716471151499, 1913008729031, 739904909659, 63520814907, 0, 0] := by
  decide +kernel

theorem rows7757 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7757 = true := by
  decide +kernel

theorem tot7757 : totK PA10K2 A10K2.t7757 = [0, 0, 0, 306993966079, 1499517783469, 2186190818278, 903673284467, 69505476621, 0, 0] := by
  decide +kernel

theorem rows7758 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7758 = true := by
  decide +kernel

theorem tot7758 : totK PA10K2 A10K2.t7758 = [0, 0, 0, 268056436594, 1133496762072, 1935231857729, 1377354574884, 240392032567, 7047025452, 0] := by
  decide +kernel

theorem rows7759 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7759 = true := by
  decide +kernel

theorem tot7759 : totK PA10K2 A10K2.t7759 = [0, 0, 0, 474683512062, 1788708889065, 2046602208814, 589461920183, 23336148269, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
