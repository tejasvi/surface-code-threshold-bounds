import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9760 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9760 = true := by
  decide +kernel

theorem tot9760 : totK PD2M8K2 D2M8K2.t9760 = [0, 0, 144931693375, 448515408525, 292518492544, 22452061178, 0, 0] := by
  decide +kernel

theorem rows9761 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9761 = true := by
  decide +kernel

theorem tot9761 : totK PD2M8K2 D2M8K2.t9761 = [0, 0, 0, 220404915921, 477702330813, 153889612503, 4811815119, 0] := by
  decide +kernel

theorem rows9762 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9762 = true := by
  decide +kernel

theorem tot9762 : totK PD2M8K2 D2M8K2.t9762 = [0, 18947402031, 18035441955, 177831467571, 429607178030, 207635082825, 16939352947, 0] := by
  decide +kernel

theorem rows9763 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9763 = true := by
  decide +kernel

theorem tot9763 : totK PD2M8K2 D2M8K2.t9763 = [0, 200092810722, 486398785013, 208312095937, 9852138406, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
