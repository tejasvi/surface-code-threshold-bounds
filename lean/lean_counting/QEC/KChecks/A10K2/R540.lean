import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2160 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2160 = true := by
  decide +kernel

theorem tot2160 : totK PA10K2 A10K2.t2160 = [0, 408924563164, 1552193660143, 1921753054450, 853802836505, 92964918007, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2161 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2161 = true := by
  decide +kernel

theorem tot2161 : totK PA10K2 A10K2.t2161 = [0, 173264853015, 1086526185437, 1890270554776, 1141243970568, 277116837660, 19313972475, 0, 0, 0] := by
  decide +kernel

theorem rows2162 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2162 = true := by
  decide +kernel

theorem tot2162 : totK PA10K2 A10K2.t2162 = [0, 299445560447, 1248344938659, 1870771185924, 1095737392211, 177544368469, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows2163 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2163 = true := by
  decide +kernel

theorem tot2163 : totK PA10K2 A10K2.t2163 = [0, 469386291323, 1815544458312, 1989427108886, 557413781334, 32846095359, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
