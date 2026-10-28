import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5720 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5720 = true := by
  decide +kernel

theorem tot5720 : totK PD2M8K2 D2M8K2.t5720 = [0, 166482498427, 397499265792, 257263298294, 76387468293, 3820764243, 0, 0] := by
  decide +kernel

theorem rows5721 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5721 = true := by
  decide +kernel

theorem tot5721 : totK PD2M8K2 D2M8K2.t5721 = [0, 155898115394, 444301656510, 282291532273, 22269570892, 0, 0, 0] := by
  decide +kernel

theorem rows5722 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5722 = true := by
  decide +kernel

theorem tot5722 : totK PD2M8K2 D2M8K2.t5722 = [0, 92037872509, 344414461430, 380578544666, 82801308438, 1232398321, 0, 0] := by
  decide +kernel

theorem rows5723 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5723 = true := by
  decide +kernel

theorem tot5723 : totK PD2M8K2 D2M8K2.t5723 = [0, 0, 270781592162, 496857065942, 126971710610, 3699256714, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
