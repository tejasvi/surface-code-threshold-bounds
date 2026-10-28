import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14764 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14764 = true := by
  decide +kernel

theorem tot14764 : totK PD2M8K2 D2M8K2.t14764 = [122978065129, 444084143549, 320126001536, 35860551272, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14765 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14765 = true := by
  decide +kernel

theorem tot14765 : totK PD2M8K2 D2M8K2.t14765 = [0, 176335592074, 447440856535, 259364379102, 25373788367, 0, 0, 0] := by
  decide +kernel

theorem rows14766 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14766 = true := by
  decide +kernel

theorem tot14766 : totK PD2M8K2 D2M8K2.t14766 = [0, 191113761667, 510106072410, 201668851108, 5430665091, 0, 0, 0] := by
  decide +kernel

theorem rows14767 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14767 = true := by
  decide +kernel

theorem tot14767 : totK PD2M8K2 D2M8K2.t14767 = [157388839447, 397641828663, 260130696435, 93089556520, 6804944647, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
