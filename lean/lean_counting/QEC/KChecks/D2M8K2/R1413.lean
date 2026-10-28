import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5652 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5652 = true := by
  decide +kernel

theorem tot5652 : totK PD2M8K2 D2M8K2.t5652 = [170810512900, 445582187052, 270160725992, 28194126733, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5653 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5653 = true := by
  decide +kernel

theorem tot5653 : totK PD2M8K2 D2M8K2.t5653 = [112781078216, 423655092575, 345375427811, 30158279275, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5654 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5654 = true := by
  decide +kernel

theorem tot5654 : totK PD2M8K2 D2M8K2.t5654 = [0, 211461786347, 495546194848, 176548838216, 4967996017, 0, 0, 0] := by
  decide +kernel

theorem rows5655 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5655 = true := by
  decide +kernel

theorem tot5655 : totK PD2M8K2 D2M8K2.t5655 = [0, 190989642388, 458123576066, 220396234620, 17080783126, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
