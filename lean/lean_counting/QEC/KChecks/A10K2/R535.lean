import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2140 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2140 = true := by
  decide +kernel

theorem tot2140 : totK PA10K2 A10K2.t2140 = [583317622402, 1871223767188, 1785180207183, 511806771455, 31941609474, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2141 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2141 = true := by
  decide +kernel

theorem tot2141 : totK PA10K2 A10K2.t2141 = [0, 1040827260419, 2393361384392, 1135688617196, 93642610035, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2142 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2142 = true := by
  decide +kernel

theorem tot2142 : totK PA10K2 A10K2.t2142 = [0, 456829410403, 1791642259633, 1832401480510, 511191757765, 31987755669, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2143 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2143 = true := by
  decide +kernel

theorem tot2143 : totK PA10K2 A10K2.t2143 = [0, 544161069420, 1927874558641, 1857047390224, 420247270440, 13149912228, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
