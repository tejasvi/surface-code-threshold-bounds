import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6772 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6772 = true := by
  decide +kernel

theorem tot6772 : totK PD2M8K2 D2M8K2.t6772 = [42834506414, 392771903026, 433823681388, 56893595429, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6773 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6773 = true := by
  decide +kernel

theorem tot6773 : totK PD2M8K2 D2M8K2.t6773 = [120245566937, 348702773892, 332696802799, 92944375405, 3869034280, 0, 0, 0] := by
  decide +kernel

theorem rows6774 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6774 = true := by
  decide +kernel

theorem tot6774 : totK PD2M8K2 D2M8K2.t6774 = [163335630369, 444592286430, 279323130727, 30158397190, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6775 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6775 = true := by
  decide +kernel

theorem tot6775 : totK PD2M8K2 D2M8K2.t6775 = [140513577858, 439362099034, 297811306995, 25633707681, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
