import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14824 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14824 = true := by
  decide +kernel

theorem tot14824 : totK PD2M8K2 D2M8K2.t14824 = [0, 75796491829, 352959101987, 376543013237, 70023952584, 1206465782, 0, 0] := by
  decide +kernel

theorem rows14825 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14825 = true := by
  decide +kernel

theorem tot14825 : totK PD2M8K2 D2M8K2.t14825 = [0, 92939194676, 392140378539, 362377994232, 35182460358, 0, 0, 0] := by
  decide +kernel

theorem rows14826 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14826 = true := by
  decide +kernel

theorem tot14826 : totK PD2M8K2 D2M8K2.t14826 = [0, 158601177604, 453541928616, 281540821911, 29170957262, 0, 0, 0] := by
  decide +kernel

theorem rows14827 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14827 = true := by
  decide +kernel

theorem tot14827 : totK PD2M8K2 D2M8K2.t14827 = [0, 166387527578, 468130065249, 247394790523, 11507628076, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
