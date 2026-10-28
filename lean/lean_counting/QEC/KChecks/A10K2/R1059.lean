import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4236 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4236 = true := by
  decide +kernel

theorem tot4236 : totK PA10K2 A10K2.t4236 = [0, 138992330854, 1222257129481, 2250726881534, 978400608305, 71494099762, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4237 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4237 = true := by
  decide +kernel

theorem tot4237 : totK PA10K2 A10K2.t4237 = [0, 486094728343, 1674841538456, 1848328657012, 797868354047, 141497682970, 5546304973, 0, 0, 0] := by
  decide +kernel

theorem rows4238 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4238 = true := by
  decide +kernel

theorem tot4238 : totK PA10K2 A10K2.t4238 = [230335522077, 862510313928, 1564530082350, 1640878621409, 648116967321, 57551169768, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4239 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4239 = true := by
  decide +kernel

theorem tot4239 : totK PA10K2 A10K2.t4239 = [550293731329, 1919368493357, 1935211639050, 520229076056, 31863753596, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
