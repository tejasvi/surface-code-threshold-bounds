import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12908 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12908 = true := by
  decide +kernel

theorem tot12908 : totK PD2M8K2 D2M8K2.t12908 = [0, 0, 83201297293, 390335849379, 346481156664, 40570555820, 0, 0] := by
  decide +kernel

theorem rows12909 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12909 = true := by
  decide +kernel

theorem tot12909 : totK PD2M8K2 D2M8K2.t12909 = [0, 0, 168581928644, 491770375514, 231553565203, 7805613361, 0, 0] := by
  decide +kernel

theorem rows12910 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12910 = true := by
  decide +kernel

theorem tot12910 : totK PD2M8K2 D2M8K2.t12910 = [0, 0, 170608052492, 456355184237, 224500020972, 13745470249, 0, 0] := by
  decide +kernel

theorem rows12911 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12911 = true := by
  decide +kernel

theorem tot12911 : totK PD2M8K2 D2M8K2.t12911 = [0, 0, 190381297397, 465868205681, 213481266318, 14867380226, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
