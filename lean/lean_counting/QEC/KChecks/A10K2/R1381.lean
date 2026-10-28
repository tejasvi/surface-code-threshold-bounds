import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5524 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5524 = true := by
  decide +kernel

theorem tot5524 : totK PA10K2 A10K2.t5524 = [0, 0, 191839120757, 1371093364140, 2230403327461, 873826347426, 65953746422, 0, 0, 0] := by
  decide +kernel

theorem rows5525 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5525 = true := by
  decide +kernel

theorem tot5525 : totK PA10K2 A10K2.t5525 = [0, 0, 486934930937, 1608684849900, 1835413376369, 883373625033, 152183166934, 6121173289, 0, 0] := by
  decide +kernel

theorem rows5526 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5526 = true := by
  decide +kernel

theorem tot5526 : totK PA10K2 A10K2.t5526 = [0, 149413146878, 664339035562, 1536615677952, 1832656567979, 746087609428, 61190578067, 0, 0, 0] := by
  decide +kernel

theorem rows5527 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5527 = true := by
  decide +kernel

theorem tot5527 : totK PA10K2 A10K2.t5527 = [0, 443825574614, 1817572615383, 2160133322595, 684889676427, 27005225143, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
