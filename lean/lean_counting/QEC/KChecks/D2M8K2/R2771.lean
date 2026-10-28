import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11084 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11084 = true := by
  decide +kernel

theorem tot11084 : totK PD2M8K2 D2M8K2.t11084 = [0, 208992467504, 470690610827, 187148899960, 11879463720, 0, 0, 0] := by
  decide +kernel

theorem rows11085 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11085 = true := by
  decide +kernel

theorem tot11085 : totK PD2M8K2 D2M8K2.t11085 = [190484942520, 453783173316, 237986435619, 26166266237, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11086 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11086 = true := by
  decide +kernel

theorem tot11086 : totK PD2M8K2 D2M8K2.t11086 = [211067643887, 467721626154, 212272966110, 12499826157, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11087 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11087 = true := by
  decide +kernel

theorem tot11087 : totK PD2M8K2 D2M8K2.t11087 = [0, 295190362793, 487762896620, 107056085678, 1198073392, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
