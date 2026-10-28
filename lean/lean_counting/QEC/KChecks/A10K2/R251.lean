import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1004 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1004 = true := by
  decide +kernel

theorem tot1004 : totK PA10K2 A10K2.t1004 = [0, 0, 0, 541125250100, 1984776977429, 1978667269322, 435383199947, 13231026584, 0, 0] := by
  decide +kernel

theorem rows1005 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1005 = true := by
  decide +kernel

theorem tot1005 : totK PA10K2 A10K2.t1005 = [0, 318853106895, 967725320497, 921752880314, 985850745238, 1226646883933, 518279520850, 49137536365, 0, 0] := by
  decide +kernel

theorem rows1006 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1006 = true := by
  decide +kernel

theorem tot1006 : totK PA10K2 A10K2.t1006 = [0, 528505283126, 1848829746151, 1898281461421, 523920927996, 32846095359, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1007 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1007 = true := by
  decide +kernel

theorem tot1007 : totK PA10K2 A10K2.t1007 = [0, 0, 680698284765, 2077968729172, 1719286825865, 404063531063, 25734533292, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
