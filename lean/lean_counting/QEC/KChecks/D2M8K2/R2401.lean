import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9604 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9604 = true := by
  decide +kernel

theorem tot9604 : totK PD2M8K2 D2M8K2.t9604 = [0, 53243889863, 338350529570, 425670811579, 73298530303, 1075657031, 0, 0] := by
  decide +kernel

theorem rows9605 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9605 = true := by
  decide +kernel

theorem tot9605 : totK PD2M8K2 D2M8K2.t9605 = [0, 56386341697, 295963420511, 406441161927, 103765207001, 3804183361, 0, 0] := by
  decide +kernel

theorem rows9606 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9606 = true := by
  decide +kernel

theorem tot9606 : totK PD2M8K2 D2M8K2.t9606 = [0, 188825886213, 457408168457, 245290333533, 20859766089, 0, 0, 0] := by
  decide +kernel

theorem rows9607 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9607 = true := by
  decide +kernel

theorem tot9607 : totK PD2M8K2 D2M8K2.t9607 = [0, 175686774192, 474574331648, 235405786012, 13461787584, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
