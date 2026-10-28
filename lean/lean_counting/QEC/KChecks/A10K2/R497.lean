import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1988 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1988 = true := by
  decide +kernel

theorem tot1988 : totK PA10K2 A10K2.t1988 = [0, 0, 0, 601193162072, 2032565468193, 1889762375559, 417488363118, 11910457242, 0, 0] := by
  decide +kernel

theorem rows1989 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1989 = true := by
  decide +kernel

theorem tot1989 : totK PA10K2 A10K2.t1989 = [0, 0, 474803355335, 1485753962917, 1595600120559, 883264779844, 359733965340, 43132710386, 0, 0] := by
  decide +kernel

theorem rows1990 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1990 = true := by
  decide +kernel

theorem tot1990 : totK PA10K2 A10K2.t1990 = [0, 0, 344472880302, 1614624212946, 2112548277324, 818496412120, 71378360188, 0, 0, 0] := by
  decide +kernel

theorem rows1991 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1991 = true := by
  decide +kernel

theorem tot1991 : totK PA10K2 A10K2.t1991 = [0, 0, 0, 512933326219, 1828590895839, 1747921426258, 479524738514, 30780440178, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
