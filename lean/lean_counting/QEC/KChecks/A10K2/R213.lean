import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows852 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t852 = true := by
  decide +kernel

theorem tot852 : totK PA10K2 A10K2.t852 = [445895346003, 1805351278873, 1930492842479, 486233141277, 25686058060, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows853 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t853 = true := by
  decide +kernel

theorem tot853 : totK PA10K2 A10K2.t853 = [297251734964, 1405071491154, 2175210671497, 1092045858046, 106720105555, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows854 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t854 = true := by
  decide +kernel

theorem tot854 : totK PA10K2 A10K2.t854 = [15638348816, 506977719300, 1825472881569, 1848011105399, 503878594008, 30831673886, 0, 0, 0, 0] := by
  decide +kernel

theorem rows855 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t855 = true := by
  decide +kernel

theorem tot855 : totK PA10K2 A10K2.t855 = [462972269471, 1824032100160, 1962553483137, 559672650251, 32066831123, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
