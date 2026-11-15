import Erdos112.KData

/-! Step 1 of the search: every graph on `J` that the search finds is one of the 24 tables of
`KData.lean`. One kernel computation (`decide +kernel`). -/

namespace Erdos112.K

theorem covered_Js : covered Js = true := by decide +kernel

end Erdos112.K
