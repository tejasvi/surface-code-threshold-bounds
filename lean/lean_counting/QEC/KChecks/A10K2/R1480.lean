import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5920 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5920 = true := by
  decide +kernel

theorem tot5920 : totK PA10K2 A10K2.t5920 = [451939543529, 1436885411863, 1744722298158, 969384008520, 168626083080, 6034215561, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5921 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5921 = true := by
  decide +kernel

theorem tot5921 : totK PA10K2 A10K2.t5921 = [290480228743, 1504897654290, 2041762440769, 718890588784, 53385992088, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5922 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5922 = true := by
  decide +kernel

theorem tot5922 : totK PA10K2 A10K2.t5922 = [0, 704162308172, 2079244002670, 1569897373442, 269313011847, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5923 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5923 = true := by
  decide +kernel

theorem tot5923 : totK PA10K2 A10K2.t5923 = [0, 442102105610, 1758131534023, 1975294929620, 544840523955, 31987876949, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
