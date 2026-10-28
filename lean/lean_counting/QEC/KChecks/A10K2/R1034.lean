import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4136 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4136 = true := by
  decide +kernel

theorem tot4136 : totK PA10K2 A10K2.t4136 = [0, 0, 455090902649, 1670727566656, 1876238155147, 596505686365, 53798373383, 0, 0, 0] := by
  decide +kernel

theorem rows4137 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4137 = true := by
  decide +kernel

theorem tot4137 : totK PA10K2 A10K2.t4137 = [0, 0, 264020895541, 1469118336283, 2054903723347, 697882217429, 45210675089, 0, 0, 0] := by
  decide +kernel

theorem rows4138 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4138 = true := by
  decide +kernel

theorem tot4138 : totK PA10K2 A10K2.t4138 = [0, 0, 296129428203, 1269649538949, 1908353033487, 968016986727, 166466959950, 5528811039, 0, 0] := by
  decide +kernel

theorem rows4139 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4139 = true := by
  decide +kernel

theorem tot4139 : totK PA10K2 A10K2.t4139 = [0, 237700837005, 1018797120747, 1766336024864, 1504442075103, 426078132459, 29010686974, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
