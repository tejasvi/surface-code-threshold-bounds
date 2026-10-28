import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7104 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7104 = true := by
  decide +kernel

theorem tot7104 : totK PA10K2 A10K2.t7104 = [0, 0, 598986562898, 2054117829337, 1999205770251, 485355930679, 27011302452, 0, 0, 0] := by
  decide +kernel

theorem rows7105 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7105 = true := by
  decide +kernel

theorem tot7105 : totK PA10K2 A10K2.t7105 = [0, 371399122619, 1210656616820, 1574548906273, 1242902852495, 535378423229, 50300197778, 0, 0, 0] := by
  decide +kernel

theorem rows7106 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7106 = true := by
  decide +kernel

theorem tot7106 : totK PA10K2 A10K2.t7106 = [0, 410425211567, 1769267211317, 2007914823463, 654316874738, 47957490282, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7107 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7107 = true := by
  decide +kernel

theorem tot7107 : totK PA10K2 A10K2.t7107 = [0, 0, 498190445702, 1940738058914, 1808461636380, 416006335286, 25371180993, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
