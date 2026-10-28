import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9676 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9676 = true := by
  decide +kernel

theorem tot9676 : totK PD2M8K2 D2M8K2.t9676 = [0, 84141673447, 307947676758, 376175823299, 112366059491, 4906626486, 0, 0] := by
  decide +kernel

theorem rows9677 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9677 = true := by
  decide +kernel

theorem tot9677 : totK PD2M8K2 D2M8K2.t9677 = [0, 177104500121, 462455617397, 253324381453, 22386196803, 0, 0, 0] := by
  decide +kernel

theorem rows9678 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9678 = true := by
  decide +kernel

theorem tot9678 : totK PD2M8K2 D2M8K2.t9678 = [0, 165290289616, 460766395097, 263877924095, 19215296813, 0, 0, 0] := by
  decide +kernel

theorem rows9679 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9679 = true := by
  decide +kernel

theorem tot9679 : totK PD2M8K2 D2M8K2.t9679 = [0, 0, 275142911751, 498017683466, 120594275732, 1268739303, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
