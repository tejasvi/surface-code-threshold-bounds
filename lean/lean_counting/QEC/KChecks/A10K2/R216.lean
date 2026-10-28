import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows864 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t864 = true := by
  decide +kernel

theorem tot864 : totK PA10K2 A10K2.t864 = [0, 291018669035, 1313276318379, 1959260965344, 1047314562434, 173817584991, 5546304973, 0, 0, 0] := by
  decide +kernel

theorem rows865 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t865 = true := by
  decide +kernel

theorem tot865 : totK PA10K2 A10K2.t865 = [0, 537525504914, 1947898970296, 2092289406981, 582164677122, 19876255495, 0, 0, 0, 0] := by
  decide +kernel

theorem rows866 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t866 = true := by
  decide +kernel

theorem tot866 : totK PA10K2 A10K2.t866 = [483357255508, 1695421881418, 1716829498952, 668017042325, 247903446001, 37674914273, 0, 0, 0, 0] := by
  decide +kernel

theorem rows867 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t867 = true := by
  decide +kernel

theorem tot867 : totK PA10K2 A10K2.t867 = [297779599935, 1461150086761, 2219874752116, 976436515361, 84571152217, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
