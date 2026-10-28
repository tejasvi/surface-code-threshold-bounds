import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5828 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5828 = true := by
  decide +kernel

theorem tot5828 : totK PA10K2 A10K2.t5828 = [0, 0, 0, 507716938849, 1756447315902, 1811329189301, 495986946518, 45824864222, 0, 0] := by
  decide +kernel

theorem rows5829 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5829 = true := by
  decide +kernel

theorem tot5829 : totK PA10K2 A10K2.t5829 = [0, 0, 0, 302082434609, 1562708460434, 2075628900379, 671101856407, 43560737560, 0, 0] := by
  decide +kernel

theorem rows5830 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5830 = true := by
  decide +kernel

theorem tot5830 : totK PA10K2 A10K2.t5830 = [0, 0, 223871224994, 557022802386, 796509214385, 1623259798280, 1166553305488, 233528391130, 6354482628, 0] := by
  decide +kernel

theorem rows5831 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5831 = true := by
  decide +kernel

theorem tot5831 : totK PA10K2 A10K2.t5831 = [0, 0, 550018211607, 1921737652992, 1958993425299, 527191490012, 32408125582, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
