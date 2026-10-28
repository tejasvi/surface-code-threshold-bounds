import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8684 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8684 = true := by
  decide +kernel

theorem tot8684 : totK PD2M8K2 D2M8K2.t8684 = [0, 189621380767, 462187071060, 232834723062, 15586905821, 0, 0, 0] := by
  decide +kernel

theorem rows8685 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8685 = true := by
  decide +kernel

theorem tot8685 : totK PD2M8K2 D2M8K2.t8685 = [0, 56561114677, 345040142532, 425661904272, 78628244692, 0, 0, 0] := by
  decide +kernel

theorem rows8686 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8686 = true := by
  decide +kernel

theorem tot8686 : totK PD2M8K2 D2M8K2.t8686 = [0, 0, 204336289397, 480323359946, 177122056344, 4627616211, 0, 0] := by
  decide +kernel

theorem rows8687 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8687 = true := by
  decide +kernel

theorem tot8687 : totK PD2M8K2 D2M8K2.t8687 = [0, 0, 154696739012, 442404918331, 293606862632, 28589021503, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
