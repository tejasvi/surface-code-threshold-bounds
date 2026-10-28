import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows164 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t164 = true := by
  decide +kernel

theorem tot164 : totK PA10K2 A10K2.t164 = [0, 475896402864, 1805541855321, 2092233420327, 682954966331, 50635882146, 0, 0, 0, 0] := by
  decide +kernel

theorem rows165 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t165 = true := by
  decide +kernel

theorem tot165 : totK PA10K2 A10K2.t165 = [300827602965, 1049460845899, 1546035668576, 1487507048310, 582995846739, 50555834002, 0, 0, 0, 0] := by
  decide +kernel

theorem rows166 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t166 = true := by
  decide +kernel

theorem tot166 : totK PA10K2 A10K2.t166 = [481111462414, 1867293915579, 2016960544364, 554437577896, 31863753596, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows167 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t167 = true := by
  decide +kernel

theorem tot167 : totK PA10K2 A10K2.t167 = [0, 666224770382, 2076738140187, 1701422601102, 393600949516, 25295400199, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
