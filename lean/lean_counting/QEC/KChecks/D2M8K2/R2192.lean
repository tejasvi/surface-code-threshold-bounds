import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8768 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8768 = true := by
  decide +kernel

theorem tot8768 : totK PD2M8K2 D2M8K2.t8768 = [0, 0, 208892082865, 483024054091, 204897905681, 8130152497, 0, 0] := by
  decide +kernel

theorem rows8769 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8769 = true := by
  decide +kernel

theorem tot8769 : totK PD2M8K2 D2M8K2.t8769 = [0, 152780043054, 357759525493, 243128077653, 122126988003, 11758933175, 0, 0] := by
  decide +kernel

theorem rows8770 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8770 = true := by
  decide +kernel

theorem tot8770 : totK PD2M8K2 D2M8K2.t8770 = [0, 170821955368, 460307514356, 235090532191, 16911962206, 0, 0, 0] := by
  decide +kernel

theorem rows8771 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8771 = true := by
  decide +kernel

theorem tot8771 : totK PD2M8K2 D2M8K2.t8771 = [0, 0, 288370552535, 506786325825, 86562091546, 1209030869, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
