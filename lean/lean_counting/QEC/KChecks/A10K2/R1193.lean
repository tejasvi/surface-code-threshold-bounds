import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4772 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4772 = true := by
  decide +kernel

theorem tot4772 : totK PA10K2 A10K2.t4772 = [0, 0, 455712486580, 1795430043639, 1979787620713, 557679514570, 32846095359, 0, 0, 0] := by
  decide +kernel

theorem rows4773 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4773 = true := by
  decide +kernel

theorem tot4773 : totK PA10K2 A10K2.t4773 = [0, 0, 105533537852, 942613130682, 2032480759132, 1370392602930, 277924734624, 20340910120, 0, 0] := by
  decide +kernel

theorem rows4774 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4774 = true := by
  decide +kernel

theorem tot4774 : totK PA10K2 A10K2.t4774 = [0, 0, 187307279949, 903100788007, 1855949185239, 1455144483304, 303053817147, 11111663730, 0, 0] := by
  decide +kernel

theorem rows4775 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4775 = true := by
  decide +kernel

theorem tot4775 : totK PA10K2 A10K2.t4775 = [0, 0, 473182244159, 1751522629578, 1900112125315, 588341844791, 37254374173, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
