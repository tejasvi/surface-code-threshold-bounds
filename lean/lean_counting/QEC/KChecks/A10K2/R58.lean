import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows232 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t232 = true := by
  decide +kernel

theorem tot232 : totK PA10K2 A10K2.t232 = [0, 0, 0, 567885791265, 1952467390106, 1688611370363, 405642512115, 25239774317, 0, 0] := by
  decide +kernel

theorem rows233 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t233 = true := by
  decide +kernel

theorem tot233 : totK PA10K2 A10K2.t233 = [0, 0, 314410996491, 1363215821643, 1951692524471, 985033030624, 163075690354, 5410721913, 0, 0] := by
  decide +kernel

theorem rows234 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t234 = true := by
  decide +kernel

theorem tot234 : totK PA10K2 A10K2.t234 = [0, 0, 401959655787, 1678769611001, 1874915869739, 487293717089, 32365810812, 0, 0, 0] := by
  decide +kernel

theorem rows235 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t235 = true := by
  decide +kernel

theorem tot235 : totK PA10K2 A10K2.t235 = [0, 0, 225182653036, 1067112270301, 1922922613288, 1107091739606, 172237192518, 5546304973, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
